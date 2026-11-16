module

public import Zkc.Core.Admission.Check
public import Zkc.Core.Facts.Soundness
public import Zkc.Core.Meaning.Program
public import Zkc.Core.Transform.StepSound

@[expose] public section

/-!
The theorem of the check of facts for a program: by induction over its definitions, when the
check accepts each function against the headers before it (`Defs.Accepted`), every function is
safe and keeps validity on valid inputs, and no loop of a function runs more often than its
bound.

With it, a program whose functions follow those of another program over the same headers
(`Defs.functionsFollow`), both accepted by the check of facts, gives every function the meaning
on valid inputs of the function of the other with its header (`Defs.functionsFollow_sound`), by
induction over the definitions: a replaced function means the same by the theorem of the
decision for functions, against the callees before it, and a function that calls a replaced
function is the
same term against callees that mean the same on valid inputs (`Term.denote_tables`).
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
      · obtain ⟨d, r⟩ := FactCheck.checkFacts_places hdr.key inputs body e1 q m
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
          · have := (FactCheck.checkFacts_places hdr.key inputs body e1 _ m').1
            simp only at this
            rw [this] at d
            exact absurd d notIn
          · exact m')
      have sound := FactCheck.checkFacts_sound (table := Defs.fnTable M rest) distinct' safeR
        keepsR hdr.key inputs body ok.distinct e1 F (fun p b m d r => by
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

/-- The functions of a program whose functions were replaced by functions that follow them mean
what they meant: when both programs are accepted by the check of facts, every function of the
second has, on valid inputs, the meaning of the function of the first with its header. The
functions that call a replaced function are covered: they call it on valid values, where it
means the same. Nothing is said of the protocols of the two programs, which are not compared. -/
theorem Defs.functionsFollow_sound : ∀ {hs : Headers V} (defs defs' : Defs V hs),
    (hs.fns.map (·.key)).Nodup → ∀ {bounds bounds' : List (Place × Nat)},
    Defs.Accepted defs bounds → Defs.Accepted defs' bounds' →
    Defs.functionsFollow defs defs' = true →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Member hs.fns hdr) (ins : HList M.Val hdr.ins),
      ins.All M.Valid → Defs.fnTable M defs' hdr f ins = Defs.fnTable M defs hdr f ins
  | _, .nil, _, _, _, _, _, _, _, _, _, f, _, _ => nomatch f
  | _, .fn (hs := hs) hdr inputs body ok rest, defs', distinct, _, _, accepted, accepted',
      follows, M, _, f, ins, valid => by
      obtain ⟨inputs', body', ok', rest', same', decided, restFollows⟩ :=
        Defs.followsFn_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl follows
      cases eq_of_heq same'
      obtain ⟨_, _, checked, restAccepted, -⟩ := accepted
      obtain ⟨_, _, checked', restAccepted', -⟩ := accepted'
      have distinct' := (List.nodup_cons.mp distinct).2
      have agree : ∀ hdr' (callee : Member hs.fns hdr') (args : HList M.Val hdr'.ins),
          args.All M.Valid → Defs.fnTable M rest' hdr' callee args =
            Defs.fnTable M rest hdr' callee args :=
        fun hdr' callee args valid' => Defs.functionsFollow_sound rest rest' distinct' restAccepted
          restAccepted' restFollows M hdr' callee args valid'
      cases f with
      | head =>
          obtain ⟨safe, keeps, -⟩ :=
            functions_sound rest distinct' restAccepted M [] (fun _ _ none => nomatch none)
          show body'.denote (localSem M _ (Defs.fnTable M rest')) []
              (Env.empty.extend inputs' ins) =
            body.denote (localSem M _ (Defs.fnTable M rest)) [] (Env.empty.extend inputs ins)
          rw [Term.denote_tables (Defs.fnTable M rest') keeps agree body' [] _
            (Env.extend_valid (fun _ x => nomatch (Ctx.find?_empty x.name).symm.trans x.typed)
              inputs' ins valid)]
          exact (functions_follow_equal inputs inputs' body body' hdr.key hdr.key ok.distinct
            ok'.distinct checked checked' decided M (Defs.fnTable M rest) distinct' safe keeps
            (Defs.fnTable_stops_undefined M rest) ins valid).symm
      | tail f => exact agree _ f ins valid
  | _, .protocol hdr _ _ _ rest, defs', distinct, _, _, accepted, accepted', follows, M, _, f,
      ins, valid => by
      obtain ⟨_, _, _, rest', same', restFollows⟩ :=
        Defs.followsProtocol_true (rest := fun rest' => Defs.functionsFollow rest rest') defs' rfl
          follows
      cases eq_of_heq same'
      exact Defs.functionsFollow_sound rest rest' distinct accepted accepted' restFollows M _ f ins
        valid

end

end Zkc.Core
