module

public import ZkcSecurity.FiatShamir.OriginalTransport

@[expose] public section

/-! Kernel-checked boundaries of unrestricted relational presentation.
These counterexamples use the existing ReadingTo, Simulation and Alignment.
-/
set_option autoImplicit false
namespace TestsSecurity.RelationalPresentationObstructions
open Zkc.Source Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir ZkcSecurity.FiatShamir.Original
open DomainReduction

abbrev carriers := Structured.uniformCarriers Bool Unit

def context : Context :=
  ⟨"entry", ["producer", "validator"], 0, 1, 0, "random.scalar/0",
    some (.draw "scalar"), "suite", []⟩

abbrev origin := context.query "draw" (.draw "scalar")
abbrev querySignature : PIR.Signature := ⟨Unit, fun _ => Unit⟩

def collapsed : Interface querySignature (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw :=
  fun _ => .query (.challenge origin) (fun _ => some ())

def source : PIR.Process (Domain.effects carriers) Unit :=
  .call (.query [] origin) fun _ => .done ()

/-- The Boolean verdict is identical; only the complete final frame differs. -/
def fullResult (raw : Bool) : Domain.Result carriers :=
  ⟨[.data (.boolean false)], [.data (.boolean raw)]⟩

def fullReturns (_ : Unit) (result : Domain.Result carriers) : Prop :=
  result.values = [.data (.boolean false)]

def target : PIR.Process (Domain.effects carriers) (Domain.Result carriers) :=
  .call (.query [] origin) fun raw => .done (fullResult raw)

def nominal : PIR.Process querySignature Unit := .call () fun _ => .done ()

/-- A valid source bridge and full simulation can lose raw-answer distinctions
at the nominal decoder, even though both raw replies remain possible. -/
def collapsedBridge : Original.Bridge collapsed (fun _ _ => True) [] source target nominal
    fullReturns (fun _ _ => True) where
  sourceReading := ⟨.query (I := querySignature) [] origin _ () (fun _ => .done ()) (fun _ => ()) rfl rfl
      (fun _ => .done _ _ trivial),
    .query [] origin _ rfl (fun _ => .done _ _ trivial)⟩
  simulation := .call (.query [] origin) (fun _ => .done rfl)

/-- Completion and even a full all-reply Alignment do hold here. Compatibility
with the actual full target returns is the remaining missing obligation. -/
theorem collapsed_has_full_alignment :
    ∃ presented : PIR.Process querySignature (Domain.Result carriers),
      Alignment fullReturns nominal presented := by
  refine ⟨.call () (fun _ => .done (fullResult false)), ?_⟩
  exact Alignment.call (I := querySignature) (returns := fullReturns) () (fun _ => .done rfl)

private theorem collapsed_done {value : Domain.Result carriers}
    {presented : PIR.Process querySignature (Domain.Result carriers)}
    (reading : ReadingTo collapsed (fun _ _ => True) [.challenge origin] (.done value) presented) :
    presented = .done value := by
  cases reading with
  | done => rfl
  | absorbSend operation next event value absorbed suffix => cases absorbed

/-- There is no target reading at all, even with a trivial target Post and
without requiring Alignment. A full target result cannot recover erased raw
information from a one-element nominal reply. -/
theorem collapsed_has_no_target_reading :
    ¬ ∃ presented : PIR.Process querySignature (Domain.Result carriers),
      ReadingTo collapsed (fun _ _ => True) [] target presented := by
  rintro ⟨presented, reading⟩
  cases reading with
  | absorbSend operation next event value absorbed suffix => cases absorbed
  | query history origin left operation next reply supported absorbed suffix =>
    have low := collapsed_done (suffix false)
    have high := collapsed_done (suffix true)
    have same : reply false = reply true := Subsingleton.elim _ _
    rw [same] at low
    have impossible := low.symm.trans high
    simp [fullResult] at impossible

abbrev sendSignature : PIR.Signature := ⟨Unit, fun _ => Bool⟩

def fixedSend : Interface sendSignature (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw :=
  fun _ => .send (.challenge origin) false

def extraReply : PIR.Process sendSignature Unit :=
  .call () fun reply => if reply then .done () else .halt .reject

/-- An undecodable reply can return a value with no related target value.
Both actual processes stop, so their simulation has no return obligation. -/
def extraReplyBridge : Original.Bridge fixedSend (fun _ _ => True) []
    (.halt .reject : PIR.Process (Domain.effects carriers) Unit)
    (.halt .reject : PIR.Process (Domain.effects carriers) Bool) extraReply
    (fun _ _ => False) (fun _ _ => True) where
  sourceReading := ⟨.absorbSend (I := sendSignature) () _ (.challenge origin) false rfl (.halt _ .reject),
    .halt _ .reject⟩
  simulation := .halt .reject

/-- All-reply Alignment cannot be derived just from a handler reading. -/
theorem extraReply_has_no_full_alignment :
    ¬ ∃ presented : PIR.Process sendSignature Bool,
      Alignment (fun (_ : Unit) (_ : Bool) => False) extraReply presented := by
  rintro ⟨presented, aligned⟩
  have noReturn : ∀ finished : PIR.Process sendSignature Bool,
      ¬ Alignment (fun (_ : Unit) (_ : Bool) => False) (.done ()) finished := by
    intro finished related
    cases related with
    | done impossible => exact impossible
  cases aligned with
  | call operation next => exact noReturn _ (next true)

end TestsSecurity.RelationalPresentationObstructions
