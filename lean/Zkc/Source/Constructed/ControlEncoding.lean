module

public import Zkc.Source.Constructed.ControlFormat
public import Zkc.Source.Constructed.Encoding

@[expose] public section

namespace Zkc.Source.Constructed.Control.Format
open Lean Constructed.Format

/-- Structural encoding retains control and all operand selections. -/
def encodeBody : RawBody → Json
  | .flat instructions returned => .arr #[.str "flat",
      encodeList encodeInstruction instructions, encodeList encodeNatural returned]
  | .sequence types first next => .arr #[.str "sequence", encodeList Json.str types,
      encodeBody first, encodeBody next]
  | .branch condition yes no => .arr #[.str "branch", encodeNatural condition,
      encodeBody yes, encodeBody no]
  | .loop maximum count carried initial captures captured iteration next =>
      .arr #[.str "loop", encodeNatural maximum, encodeNatural count,
        encodeList Json.str carried, encodeList encodeNatural initial,
        encodeList Json.str captures, encodeList encodeNatural captured,
        encodeBody iteration, encodeBody next]

def fitsBody : Nat → RawBody → Bool
  | 0, _ => false
  | _ + 1, .flat instructions returned =>
      fitsList fitsInstruction instructions && fitsList fitsNatural returned
  | depth + 1, .sequence types first next =>
      fitsList fitsText types && fitsBody depth first && fitsBody depth next
  | depth + 1, .branch condition yes no =>
      fitsNatural condition && fitsBody depth yes && fitsBody depth no
  | depth + 1, .loop maximum count carried initial captures captured iteration next =>
      fitsNatural maximum && fitsNatural count && fitsList fitsText carried &&
      fitsList fitsNatural initial && fitsList fitsText captures && fitsList fitsNatural captured &&
      fitsBody depth iteration && fitsBody depth next

theorem body_encode (depth : Nat) (b : RawBody) (valid : fitsBody depth b = true) :
    body depth (encodeBody b) = .ok b := by
  induction depth generalizing b with
  | zero => simp [fitsBody] at valid
  | succ depth ih =>
      cases b with
      | flat instructions returned =>
          simp only [fitsBody, Bool.and_eq_true] at valid
          simp [body, encodeBody, Source.Format.array, Bind.bind, Except.bind, Pure.pure, Except.pure,
            list_encode encodeInstruction instruction fitsInstruction instruction_encode _ valid.1,
            list_encode encodeNatural natural fitsNatural natural_encode _ valid.2]
      | sequence types first next =>
          simp only [fitsBody, Bool.and_eq_true] at valid
          simp [body, encodeBody, Source.Format.array, Bind.bind, Except.bind, Pure.pure, Except.pure,
            list_encode Json.str text fitsText text_encode _ valid.1.1,
            ih first valid.1.2, ih next valid.2]
      | branch condition yes no =>
          simp only [fitsBody, Bool.and_eq_true] at valid
          simp [body, encodeBody, Source.Format.array, Bind.bind, Except.bind, Pure.pure, Except.pure,
            natural_encode _ valid.1.1, ih yes valid.1.2, ih no valid.2]
      | loop maximum count carried initial captures captured iteration next =>
          simp only [fitsBody, Bool.and_eq_true] at valid
          obtain ⟨⟨⟨⟨⟨⟨⟨hm, hc⟩, ht⟩, hi⟩, hct⟩, hcv⟩, hb⟩, hn⟩ := valid
          simp [body, encodeBody, Source.Format.array, Bind.bind, Except.bind, Pure.pure, Except.pure,
            natural_encode _ hm, natural_encode _ hc,
            list_encode Json.str text fitsText text_encode _ ht,
            list_encode encodeNatural natural fitsNatural natural_encode _ hi,
            list_encode Json.str text fitsText text_encode _ hct,
            list_encode encodeNatural natural fitsNatural natural_encode _ hcv,
            ih iteration hb, ih next hn]

def encodeSnapshot (s : Snapshot) : Json :=
  .arr #[.str "zkc.constructed-control/0", .str s.source, .str s.candidate, .str s.entry,
    .str s.role, .str s.participant, .str s.policy, encodeList encodeHandler s.handlers,
    encodeList Json.str s.inputs, encodeList Json.str s.outputs, encodeBody s.body]

def fitsSnapshot (s : Snapshot) : Bool :=
  fitsText s.source && fitsText s.candidate && fitsText s.entry && fitsText s.role &&
    fitsText s.participant && fitsText s.policy && fitsList fitsHandler s.handlers &&
    fitsList fitsText s.inputs && fitsList fitsText s.outputs && fitsBody 64 s.body

theorem snapshot_encode (s : Snapshot) (valid : fitsSnapshot s = true) :
    snapshot (encodeSnapshot s) = .ok s := by
  simp only [fitsSnapshot, Bool.and_eq_true] at valid
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨source, candidate⟩, entry⟩, role⟩, participant⟩, policy⟩,
    handlers⟩, inputs⟩, outputs⟩, control⟩ := valid
  simp [snapshot, encodeSnapshot, Source.Format.array, Bind.bind, Except.bind, Pure.pure, Except.pure,
    text_encode _ source, text_encode _ candidate, text_encode _ entry, text_encode _ role,
    text_encode _ participant, text_encode _ policy,
    list_encode encodeHandler handler fitsHandler handler_encode _ handlers,
    list_encode Json.str text fitsText text_encode _ inputs,
    list_encode Json.str text fitsText text_encode _ outputs, body_encode _ _ control]

end Zkc.Source.Constructed.Control.Format
