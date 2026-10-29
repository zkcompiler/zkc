module
public import Zkc.Construction.OriginalLoop
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Tests.OriginalCaptureReads
open Zkc.Source Zkc.Source.Structured Zkc.Construction
example {α : Type} (captured : List α) (offset : Nat) (size : captured.length = offset)
    (a b c d e f : α) :
    (captured ++ [a,b,c,d] ++ [e] ++ [f])[offset + 5]? = some f := by
  simp (disch := omega) only [List.append_assoc, List.cons_append, List.nil_append,
    List.getElem?_append_left, List.getElem?_append_right, size, Nat.add_sub_cancel_left,
    Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ]

example {carriers : Carriers} (captured : Domain.Environment carriers)
    (offset layerRef layer : Nat) (size : captured.length = offset)
    (layerRead : captured[layerRef]? = some (.data (.index layer)))
    (a b c d e : Domain.Value carriers) :
    Original.Simulation (fun (_ : Unit) frame => frame =
      captured ++ [a,b,c,d,e,.indices [],.indices [layer]])
      (fun _ frame => ArtifactBinding.Captures captured frame)
      (.done ())
      (Domain.View.indicesAppend (offset + 5) layerRef [.indices]
        (captured ++ [a,b,c,d] ++ [e] ++ [.indices []])) := by
  have inside : layerRef < offset := by
    rw [← size]; exact (List.getElem?_eq_some_iff.mp layerRead).choose
  simp only [Domain.View.indicesAppend, Domain.View.append]
  conv => arg 4; simp (disch := omega) only
    [List.append_assoc, List.cons_append, List.nil_append, List.length_cons, List.length_nil,
     List.getElem?_append_left, List.getElem?_append_right, size, inside, layerRead,
     Nat.add_sub_cancel_left, Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact .done rfl
example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = 10)
    (initial add mul point : List F) (layers selector width layer : Nat)
    (history : Domain.History (uniformCarriers F G))
    (inputRead : captured[0]? = some (.data (.vector "bls12-381.fr" initial)))
    (addRead : captured[1]? = some (.data (.vector "bls12-381.fr" add)))
    (mulRead : captured[2]? = some (.data (.vector "bls12-381.fr" mul)))
    (layersRead : captured[3]? = some (.data (.index layers)))
    (selectorRead : captured[4]? = some (.data (.index selector)))
    (widthRead : captured[5]? = some (.data (.index width))) :
    Domain.read (captured ++ [.data (.index layer), .data (.vector "bls12-381.fr" point),
      .transcript "merlin3.bls12-381.fr64be/0" history]) [1,2,0,3,4,5,10] =
    Domain.encodeValues (carriers := uniformCarriers F G)
      ((.cons add (.cons mul (.cons initial (.cons layers (.cons selector (.cons width (.cons layer .nil))))))) :
        Values (assignment F G) [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .index, .index]) := by
  simp (disch := omega) only [Domain.read, List.mapM_cons, List.mapM_nil, Domain.encodeValues,
    Domain.Value.encode, Domain.Payload.ofValue, Ty.isHandle,
    List.getElem?_append_left, List.getElem?_append_right,
    size, inputRead, addRead, mulRead, layersRead, selectorRead, widthRead,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.cons_append, List.nil_append,
    Bind.bind, Option.bind, Option.pure_def, Nat.sub_self, Nat.add_sub_cancel_left]; rfl

example {carriers : Carriers} (captured allocated first second frame : Domain.Environment carriers) :
    ArtifactBinding.Captures (((captured ++ allocated) ++ first) ++ second) frame →
      ArtifactBinding.Captures captured frame := by
  intros
  simp only [List.append_assoc] at *
  exact ArtifactBinding.captures_trans (outer := ArtifactBinding.captures_append _ _) (inner := by assumption)

end Tests.OriginalCaptureReads
