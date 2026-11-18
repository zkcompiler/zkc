module

public import Zkc.Core.Transform.Assured

@[expose] public section

/-! Function admission and replacement with externally proved laws or facts. -/

namespace Zkc.Core

open BodyAnalysis

variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}

/-- Admit this function using its stored annotations and a registry justified by the producer.
Diagnostics use the same operation, operand and lexical-site records as plain admission. -/
def TypedFn.admitAnnotated (f : TypedFn V hs hdr) (catalog : FunctionContracts hs)
    (lemmas : List (Lemma V.Ty (LocalRaw V))) (evidence : catalog.AnnotationEvidence f lemmas f.notes) :
    Except (List (ProgramRefusal V)) (AssuredFn V hs hdr) :=
  match checked : catalog.checkFunction f lemmas f.notes with
  | .error reason => .error (FunctionReport.body catalog f f lemmas reason).1
  | .ok bounds => .ok ⟨f, bounds, catalog.checkAnnotated_assured f evidence checked⟩

/-- A producer justifies the candidate's annotations. The source already carries its safety.
The returned proof relates the meaning of the two stored bodies for every legal call. -/
def AssuredFn.stepAnnotated (source : AssuredFn V hs hdr) (candidate : TypedFn V hs hdr)
    (catalog : FunctionContracts hs) (lemmas : List (Lemma V.Ty (LocalRaw V)))
    (evidence : catalog.AnnotationEvidence candidate lemmas candidate.notes) :
    Except (StepRefusal V) { next : AssuredFn V hs hdr // source.fn.SameAs next.fn } :=
  match checked : catalog.compareFunctions source.fn candidate lemmas source.fn.notes candidate.notes with
  | .error reason =>
    match FunctionReport.body catalog source.fn candidate lemmas reason with
    | ([], places) => .error (.differs places)
    | (refusals, places) => .error (.target refusals places)
  | .ok bounds =>
    let sound := catalog.compareAnnotated_assured source.fn candidate source.assured.safe evidence checked
    .ok ⟨⟨candidate, bounds, sound.1⟩, sound.2⟩

end Zkc.Core
