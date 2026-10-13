module

public import Zkc.Source.Constructed.Format

@[expose] public section

/-! Compositional structural-codec proofs. Text parsing is outside this model.
The encoder is used for kernel comparison with the independently retained JSON
tree; it is not an alternate native exporter or an authentication mechanism. -/

namespace Zkc.Source.Constructed.Format
open Lean

def encodeList {A : Type} (encode : A → Json) (values : List A) : Json :=
  .arr (values.map encode).toArray

def encodeNatural (value : Nat) : Json := .num ⟨Int.ofNat value, 0⟩
/-- Every String is structurally representable; runtime byte limits belong to preflight. -/
def fitsText (_value : String) : Bool := true
def fitsNatural (value : Nat) : Bool := value ≤ 8192
def fitsList {A : Type} (fits : A → Bool) (values : List A) : Bool :=
  values.length ≤ 2048 && values.all fits

theorem text_encode (value : String) (_fits : fitsText value = true) :
    text (.str value) = .ok value := rfl

theorem natural_encode (value : Nat) (fits : fitsNatural value = true) :
    natural (encodeNatural value) = .ok value := by
  simp only [fitsNatural, decide_eq_true_eq] at fits
  change (if value > 8192 then Except.error Source.Format.Error.natural else Except.ok value) = .ok value
  simp [Nat.not_lt_of_ge fits]

theorem list_encode {A : Type} (encode : A → Json) (decode : Json → Decode A)
    (fits : A → Bool) (roundtrip : ∀ value, fits value = true → decode (encode value) = .ok value)
    (values : List A) (valid : fitsList fits values = true) :
    list decode (encodeList encode values) = .ok values := by
  have limits : values.length ≤ 2048 ∧ (∀ value ∈ values, fits value = true) := by
    simpa only [fitsList, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using valid
  obtain ⟨length, all⟩ := limits
  have mapped : (values.map encode).mapM decode = .ok values := by
    clear valid length
    induction values with
    | nil => rfl
    | cons value rest ih =>
        simp only [List.map_cons, List.mapM_cons, roundtrip value (all value (by simp))]
        have tail := ih (fun x hx => all x (by simp [hx]))
        simp [tail, Bind.bind, Except.bind, Pure.pure, Except.pure]

  simpa [list, encodeList, Source.Format.array, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Nat.not_lt_of_ge length] using mapped

def encodePrimitive (p : Primitive) : Json :=
  .arr #[.str p.name, .str p.attributes, .str p.binding, .str p.origin,
    encodeList Json.str p.arguments, encodeList Json.str p.results]

def fitsPrimitive (p : Primitive) : Bool :=
  fitsText p.name && fitsText p.attributes && fitsText p.binding && fitsText p.origin &&
    fitsList fitsText p.arguments && fitsList fitsText p.results

theorem primitive_encode (p : Primitive) (valid : fitsPrimitive p = true) :
    primitive (encodePrimitive p) = .ok p := by
  simp only [fitsPrimitive, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨name, attrs⟩, binding⟩, origin⟩, arguments⟩, results⟩ := valid
  simp [primitive, encodePrimitive, Source.Format.array, Bind.bind,
    Except.bind, Pure.pure, Except.pure, text_encode _ name, text_encode _ attrs,
    text_encode _ binding, text_encode _ origin,
    list_encode Json.str text fitsText text_encode _ arguments,
    list_encode Json.str text fitsText text_encode _ results]

def encodeHandler (h : Handler) : Json := .arr #[.str h.name, .str h.digest, .str h.body]
def fitsHandler (h : Handler) : Bool := fitsText h.name && fitsText h.digest && fitsText h.body

theorem handler_encode (h : Handler) (valid : fitsHandler h = true) :
    handler (encodeHandler h) = .ok h := by
  simp only [fitsHandler, Bool.and_eq_true] at valid
  obtain ⟨⟨name, digest⟩, body⟩ := valid
  simp [handler, encodeHandler, Source.Format.array, Bind.bind,
    Except.bind, Pure.pure, Except.pure, text_encode _ name, text_encode _ digest, text_encode _ body]

def encodeInstruction : Instruction → Json
  | .apply op arguments => .arr #[.str "apply", encodePrimitive op, encodeList encodeNatural arguments]
  | .project types index tuple =>
      .arr #[.str "project", encodeList Json.str types, encodeNatural index, encodeNatural tuple]
  | .guard condition attrs => .arr #[.str "guard", encodeNatural condition, .str attrs]
  | .stop reason attrs => .arr #[.str "stop", Source.Format.stop.encode reason, .str attrs]

def fitsInstruction : Instruction → Bool
  | .apply op arguments => fitsPrimitive op && fitsList fitsNatural arguments
  | .project types index tuple => fitsList fitsText types && fitsNatural index && fitsNatural tuple
  | .guard condition attrs => fitsNatural condition && fitsText attrs
  | .stop _ attrs => fitsText attrs

theorem instruction_encode (i : Instruction) (valid : fitsInstruction i = true) :
    instruction (encodeInstruction i) = .ok i := by
  cases i with
  | apply op arguments =>
      have conditions : fitsPrimitive op = true ∧ fitsList fitsNatural arguments = true := by
        simpa only [fitsInstruction, Bool.and_eq_true] using valid
      obtain ⟨opValid, argsValid⟩ := conditions
      simp [instruction, encodeInstruction, Source.Format.array, Bind.bind,
        Except.bind, Pure.pure, Except.pure, primitive_encode _ opValid,
        list_encode encodeNatural natural fitsNatural natural_encode _ argsValid]
  | project types index tuple =>
      obtain ⟨⟨typesValid, indexValid⟩, tupleValid⟩ := by
        simpa only [fitsInstruction, Bool.and_eq_true] using valid
      simp [instruction, encodeInstruction, Source.Format.array, Bind.bind,
        Except.bind, Pure.pure, Except.pure, natural_encode _ indexValid, natural_encode _ tupleValid,
        list_encode Json.str text fitsText text_encode _ typesValid]
  | guard condition attrs =>
      have conditions : fitsNatural condition = true ∧ fitsText attrs = true := by
        simpa only [fitsInstruction, Bool.and_eq_true] using valid
      obtain ⟨conditionValid, attrsValid⟩ := conditions
      simp [instruction, encodeInstruction, Source.Format.array, Bind.bind,
        Except.bind, Pure.pure, Except.pure, natural_encode _ conditionValid, text_encode _ attrsValid]
  | stop reason attrs =>
      have attrsValid : fitsText attrs = true := valid
      cases reason <;> simp [instruction, encodeInstruction, Source.Format.array, Source.Format.stop,
        Bind.bind, Except.bind, Pure.pure, Except.pure, text_encode _ attrsValid]

def encodeSnapshot (s : Snapshot) : Json :=
  .arr #[.str "zkc.constructed-source/0", .str s.source, .str s.candidate, .str s.entry,
    .str s.role, .str s.participant, .str s.policy, encodeList encodeHandler s.handlers,
    encodeList Json.str s.inputs, encodeList Json.str s.outputs,
    encodeList encodeInstruction s.instructions, encodeList encodeNatural s.returned]

def fitsSnapshot (s : Snapshot) : Bool :=
  fitsText s.source && fitsText s.candidate && fitsText s.entry && fitsText s.role &&
    fitsText s.participant && fitsText s.policy && fitsList fitsHandler s.handlers &&
    fitsList fitsText s.inputs && fitsList fitsText s.outputs &&
    fitsList fitsInstruction s.instructions && fitsList fitsNatural s.returned

theorem snapshot_encode (s : Snapshot) (valid : fitsSnapshot s = true) :
    snapshot (encodeSnapshot s) = .ok s := by
  simp only [fitsSnapshot, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨source, candidate⟩, entry⟩, role⟩, participant⟩, policy⟩,
    handlers⟩, inputs⟩, outputs⟩, instructions⟩, returned⟩ := valid
  simp [snapshot, encodeSnapshot, Source.Format.array, Bind.bind,
    Except.bind, Pure.pure, Except.pure, text_encode _ source, text_encode _ candidate,
    text_encode _ entry, text_encode _ role, text_encode _ participant, text_encode _ policy,
    list_encode encodeHandler handler fitsHandler handler_encode _ handlers,
    list_encode Json.str text fitsText text_encode _ inputs,
    list_encode Json.str text fitsText text_encode _ outputs,
    list_encode encodeInstruction instruction fitsInstruction instruction_encode _ instructions,
    list_encode encodeNatural natural fitsNatural natural_encode _ returned]

end Zkc.Source.Constructed.Format
