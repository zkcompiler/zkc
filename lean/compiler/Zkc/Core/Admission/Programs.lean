module

public import Zkc.Core.Admission.Check
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Transform.StepSound

@[expose] public section

/-!
The theorem of the check of facts for a program: by induction over its definitions, when the
check accepts each function against the headers before it (`Defs.Accepted`), every function is
safe and keeps validity on valid inputs, and no loop of a function runs more often than its
bound.

The callees of a function of a program are the functions before it; that those whose headers say
that they cannot stop stop only `undefined` needs no check of facts
(`Defs.fnTable_stops_undefined`, `Meaning/Stops.lean`).

With it, a program whose functions follow those of another program over the same headers
(`Defs.functionsFollow`), of which only the other is accepted by the check of facts, gives every
function the meaning on valid inputs of the function of the other with its header, and its
functions are safe and keep validity (`Defs.functionsFollow_sound`), by induction over the
definitions: a replaced function follows a function that the check accepts, so it is safe and
means the same against the callees before it (`Analysis.follow_assured`), and against its own
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
          checkFacts_places (localFactRules V _) (localSkelRules V _) hdr.key none inputs body e1 q m
        exact ⟨by rw [d]; exact List.mem_cons_self, r⟩
      · obtain ⟨d, r⟩ := accepted_places rest e2 q m
        exact ⟨List.mem_cons_of_mem _ d, r⟩
  | _, .protocol _ _ _ _ rest, bounds, h, q, m => accepted_places rest h q m

/-- **The check of facts is sound for the functions of a program.** When the check accepts every
function of a program against the headers before it, and the keys of the functions are distinct:
every function never stops `undefined` on valid inputs, returns valid values, and on valid inputs
none of its loops runs more often than the bound that an annotation gives it, for every
annotation whose entries at the functions' places are among the bounds that the check gives. -/
theorem functions_sound : ∀ {hs : Headers V} (defs : Defs V hs),
    (hs.fns.map (·.key)).Nodup → ∀ {bounds : List (Place × Nat)},
    Defs.Accepted defs bounds → ∀ (M : Model V) (F : List (Place × Nat)),
    (∀ p b, (p, b) ∈ F → p.role = none → p.definition ∈ hs.fns.map (·.key) → (p, b) ∈ bounds) →
    FnTable.Safe (Defs.fnTable M defs) ∧ FnTable.KeepsValidity (Defs.fnTable M defs) ∧
      Defs.FunctionsRespect M ⟨F⟩ defs
  | _, .nil, _, _, _, M, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), trivial⟩
  | _, .fn (hs := hs) hdr inputs body ok rest, distinct, bounds, h, M, F, hF => by
      obtain ⟨mine, others, e1, e2, rfl⟩ := h
      have notIn := (List.nodup_cons.mp distinct).1
      have distinct' := (List.nodup_cons.mp distinct).2
      obtain ⟨safeR, keepsR, respR⟩ := functions_sound rest distinct' e2 M F
        (fun p b m r d => by
          rcases List.mem_append.mp (hF p b m r (List.mem_cons_of_mem _ d)) with m' | m'
          · have := (checkFacts_places (localFactRules V _) (localSkelRules V _) hdr.key none inputs
              body e1 _ m').1
            simp only at this
            rw [this] at d
            exact absurd d notIn
          · exact m')
      have sound := checkFacts_sound (table := Defs.fnTable M rest)
        ⟨distinct', safeR, keepsR, Defs.fnTable_stops_undefined M rest⟩ hdr.key inputs body
        ok.distinct e1 F (fun p b m d r => by
          rcases List.mem_append.mp (hF p b m r (by rw [d]; exact List.mem_cons_self)) with
            m' | m'
          · exact m'
          · have := (accepted_places rest e2 _ m').1
            simp only at this
            rw [d] at this
            exact absurd this notIn)
      refine ⟨fun hdr' f args valid => ?_, fun hdr' f args results valid e => ?_,
        fun ins valid => (sound ins valid).1, respR⟩
      · cases f with
        | head =>
            simp only [Defs.fnTable]
            exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) (sound args valid).2
        | tail f => exact safeR _ f args valid
      · cases f with
        | head =>
            simp only [Defs.fnTable] at e
            have := (sound args valid).2
            rw [e] at this
            exact this
        | tail f => exact keepsR _ f args results valid e
  | _, .protocol _ _ _ _ rest, distinct, _, h, M, F, hF => by
      obtain ⟨safeR, keepsR, respR⟩ := functions_sound rest distinct h M F hF
      exact ⟨safeR, keepsR, respR⟩

/-- **The check of facts is sound for a typed program.** When the check accepts every function of
a typed program: every function never stops `undefined` on valid inputs and returns valid values
(what `functionsSafe` and `functionsKeepValidity` ask of an admitted program), and the functions'
part of `Respects` holds of the bounds that the check gives. -/
theorem typed_functions_sound (p : Typed V) {bounds : List (Place × Nat)}
    (accepted : Defs.Accepted p.defs bounds) (M : Model V) :
    (∀ hdr (f : Member p.headers.fns hdr) (ins : HList M.Val hdr.ins), ins.All M.Valid →
      (fnMeaning M p f ins).Stops (· ≠ .undefined)) ∧
    (∀ hdr (f : Member p.headers.fns hdr) (ins : HList M.Val hdr.ins)
      (outs : HList M.Val hdr.outs), ins.All M.Valid → fnMeaning M p f ins = .done outs →
        outs.All M.Valid) ∧
    Defs.FunctionsRespect M ⟨bounds⟩ p.defs := by
  have distinct := (List.nodup_append.mp p.distinct).1
  obtain ⟨safe, keeps, respect⟩ := functions_sound p.defs distinct accepted M bounds
    (fun _ _ m _ _ => m)
  exact ⟨fun hdr f ins valid => safe hdr f ins valid,
    fun hdr f ins outs valid e => keeps hdr f ins outs valid e, respect⟩

open FactCheck in
/-- **The functions of a program whose functions were replaced by functions that follow them
mean what they meant, and are safe.** When the first program is accepted by the check of facts,
the keys of its functions are distinct, and the functions of the second follow those of the first
one by one (each with no refusal and no place that differs): every function of the second has, on
valid inputs, the meaning of the function of the first with its header, and the functions of the
second never stop `undefined` on valid inputs and keep validity. The functions that call a
replaced function are covered: they call it on valid values, where it means the same. The second
program is not asked to be accepted: each of its functions is safe because it follows a safe
function (`Analysis.follow_assured`). Nothing is said of the protocols of the two programs,
which are not compared. -/
theorem Defs.functionsFollow_sound : ∀ {hs : Headers V} (defs defs' : Defs V hs),
    (hs.fns.map (·.key)).Nodup → ∀ {bounds : List (Place × Nat)}, Defs.Accepted defs bounds →
    Defs.functionsFollow defs defs' = true → ∀ (M : Model V),
      (∀ (hdr : FnHeader V) (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins),
        ins.All M.Valid → Defs.fnTable M defs' hdr f ins = Defs.fnTable M defs hdr f ins) ∧
      FnTable.Safe (Defs.fnTable M defs') ∧ FnTable.KeepsValidity (Defs.fnTable M defs')
  | _, .nil, _, _, _, _, _, _ =>
      ⟨fun _ f => (nomatch f), fun _ f => (nomatch f), fun _ f => (nomatch f)⟩
  | _, .fn (hs := hs) hdr inputs body ok rest, defs', distinct, _, accepted, follows, M => by
      obtain ⟨inputs', body', ok', rest', same', followed, restFollows⟩ :=
        Defs.followsFn_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl follows
      cases eq_of_heq same'
      obtain ⟨_, _, checked, restAccepted, -⟩ := accepted
      have distinct' := (List.nodup_cons.mp distinct).2
      obtain ⟨agree, safe', keeps'⟩ :=
        Defs.functionsFollow_sound rest rest' distinct' restAccepted restFollows M
      obtain ⟨safe, keeps, -⟩ :=
        functions_sound rest distinct' restAccepted M [] (fun _ _ none => nomatch none)
      have callees : Callees M (Defs.fnTable M rest) :=
        ⟨distinct', safe, keeps, Defs.fnTable_stops_undefined M rest⟩
      -- the second's function, against the callees of the first: it follows a safe function
      have head := fun (ins : HList M.Val hdr.ins) (valid : ins.All M.Valid) =>
        Analysis.follow_assured (localFactRules V hs.fns) (localSkelRules V hs.fns)
          (localSem M hs.fns (Defs.fnTable M rest)) (fun _ _ => True) (localReading M)
          (LocalReturns M (Defs.fnTable M rest)) (ValidDyn M) (· = .undefined)
          (localFactRules_lawful M (Defs.fnTable M rest) distinct' safe keeps callees.quiet _)
          (localSkelRules_lawful distinct') hdr.key hdr.key none inputs inputs' body body'
          ok'.distinct followed [] (fun _ _ none => nomatch none) ins
          (by rw [localDyns_eq_toDyns M (Defs.fnTable M rest)]; exact toDyns_valid valid)
          (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h)
            (checkFacts_sound callees hdr.key inputs body ok.distinct checked []
              (fun _ _ none => nomatch none) ins valid).2)
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
            exact (Process.SameWhen.eq_of_noSig (head ins valid).2.2).symm
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
            have returned' : ∀ v, v ∈ (localSem M hs.fns (Defs.fnTable M rest)).dyns results →
                ValidDyn M v := returned
            rw [localDyns_eq_toDyns M (Defs.fnTable M rest)] at returned'
            exact valid_of_toDyns returned'
        | tail f => exact keeps' _ f args results valid ran
  | _, .protocol hdr _ _ _ rest, defs', distinct, _, accepted, follows, M => by
      obtain ⟨_, _, _, rest', same', restFollows⟩ :=
        Defs.followsProtocol_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl
          follows
      cases eq_of_heq same'
      exact Defs.functionsFollow_sound rest rest' distinct accepted restFollows M

end

end Zkc.Core
