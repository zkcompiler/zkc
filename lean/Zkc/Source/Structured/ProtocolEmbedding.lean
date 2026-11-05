module

public import Zkc.Source.RegionInterpretation
public import Zkc.Source.Finite

@[expose] public section

/-! Naturality on the existing Region and Process, with an explicit syntactic fragment.
The operation law quantifies over arbitrary callbacks and every input; it never assumes
that a callback returns, or that an external reply is honest. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source

variable {T : Type} {V W : T → Type} {I J : PIR.Signature}

def mapValues (f : (t : T) → V t → W t) : {ts : List T} → Values V ts → Values W ts
  | _, .nil => .nil
  | t :: _, .cons value rest => .cons (f t value) (mapValues f rest)

@[simp] theorem mapValues_get (f : (t : T) → V t → W t) {ts : List T} {t : T}
    (values : Values V ts) (ref : Var ts t) :
    (mapValues f values).get ref = f t (values.get ref) := by
  induction values with
  | nil => cases ref
  | cons value rest ih => cases ref with
    | here => rfl
    | there ref => exact ih ref

theorem mapValues_environment (f : (t : T) → V t → W t) {ts : List T}
    (values : Values V ts) :
    @Eq (Environment W ts) (mapValues f values).get
      (fun {t} ref ↦ f t (values.get ref)) := by
  funext t ref
  exact mapValues_get f values ref

@[simp] theorem mapValues_append (f : (t : T) → V t → W t) {ts us : List T}
    (values : Values V ts) (rest : Values V us) :
    mapValues f (values.append rest) = (mapValues f values).append (mapValues f rest) := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [mapValues, Values.append, ih]

@[simp] theorem mapValues_split (f : (t : T) → V t → W t) (ts : List T) {us : List T}
    (values : Values V (ts ++ us)) :
    (mapValues f values).split ts =
      (mapValues f (values.split ts).1, mapValues f (values.split ts).2) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases values with
    | cons value rest => simp only [mapValues, Values.split, ih]

@[simp] theorem mapValues_eval (f : (t : T) → V t → W t) {ts us : List T}
    (env : Environment V ts) (args : Operands ts us) :
    args.eval (fun {t} (ref : Var ts t) ↦ f t (env ref)) = mapValues f (args.eval env) := by
  induction args with
  | nil => rfl
  | cons value rest ih => simp only [Operands.eval, mapValues, ih]

theorem map_prepend (f : (t : T) → V t → W t) {ts us : List T}
    (env : Environment V ts) (values : Values V us) :
    @Eq (Environment W (us ++ ts))
      (fun {t} ref ↦ f t (env.prepend values ref))
      (Environment.prepend (fun {t} ref ↦ f t (env ref)) (mapValues f values)) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    funext t ref
    cases ref with
    | here => rfl
    | there ref => exact congrFun (congrFun ih _) ref

variable {d : Dialect}
mutual
  def Fragment (allowed : d.Op → Prop) {ts us} : Region d ts us → Prop
    | .ret _ | .stop _ => True
    | .letOp op _ bodies next => allowed op ∧ Fragments allowed bodies ∧ Fragment allowed next
    | .bind body next => Fragment allowed body ∧ Fragment allowed next
  def Fragments (allowed : d.Op → Prop) {ss} : Regions d ss → Prop
    | .nil => True
    | .cons body rest => Fragment allowed body ∧ Fragments allowed rest
end

/-- A callback relation has no return/completeness postcondition. Equality is over the
complete free process, including every reply-dependent continuation and stop. -/
def CallbacksCommute {V W : d.Ty → Type} (f : (t : d.Ty) → V t → W t)
    (erase : PIR.OperationInterpretation J I) {ss}
    (ordinary : Values (RegionFunction V I) ss) (lazy : Values (RegionFunction W J) ss) : Prop :=
  ∀ {signature} (ref : Var ss signature) args,
    ((lazy.get ref) (mapValues f args)).interpret erase =
      ((ordinary.get ref) args).bind (fun result ↦ .done (mapValues f result))

theorem region_naturality
    (ordinary : RegionMeaning d I) (lazy : RegionMeaning d J)
    (f : (t : d.Ty) → ordinary.Value t → lazy.Value t) (erase : PIR.OperationInterpretation J I)
    (allowed : d.Op → Prop)
    (law : ∀ op, allowed op → ∀ args left right,
      CallbacksCommute f erase left right →
      (lazy.operation op (mapValues f args) right).interpret erase =
        (ordinary.operation op args left).bind
          (fun result ↦ .done (mapValues f result)))
    {ts us} (body : Region d ts us) (fragment : Fragment allowed body)
    (env : Environment ordinary.Value ts) :
    (body.denote lazy (fun {t} (ref : Var ts t) ↦ f t (env ref))).interpret erase =
      (body.denote ordinary env).bind
        (fun result ↦ .done (mapValues f result)) := by
  revert fragment env
  induction body using Region.rec
      (motive_2 := fun ss bodies ↦ Fragments allowed bodies →
        CallbacksCommute f erase (bodies.denote ordinary) (bodies.denote lazy)) with
  | ret args =>
    intro _ env
    simp only [Region.denote, PIR.Process.interpret, PIR.Process.bind, mapValues_eval]
  | stop reason => intro _ env; rfl
  | letOp op args bodies next bodiesIH nextIH =>
    intro fragment env
    simp only [Region.denote, PIR.Process.interpret_bind, mapValues_eval]
    rw [law op fragment.1 _ _ _ (bodiesIH fragment.2.1)]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext result
    rw [← map_prepend]
    exact nextIH fragment.2.2 _
  | bind body next bodyIH nextIH =>
    intro fragment env
    simp only [Region.denote, PIR.Process.interpret_bind]
    rw [bodyIH fragment.1]
    simp only [PIR.Process.bind_assoc, PIR.Process.bind]
    congr 1
    funext result
    rw [← map_prepend]
    exact nextIH fragment.2 _
  | nil =>
    rename_i fragment
    intro signature ref
    cases ref
  | cons body rest bodyIH restIH =>
    rename_i fragment
    intro signature ref args
    cases ref with
    | here =>
      simpa only [Regions.denote, Values.get, mapValues_environment] using
        bodyIH fragment.1 args.get
    | there ref => exact restIH fragment.2 ref args

end Zkc.Source.Structured.ProtocolEmbedding

namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source

/-- Naturality of the existing finite executor, including partial/effectful steps. -/
theorem fold_naturality {I : PIR.Signature} {A S U : Type} (f : S → U)
    (left : S → A → PIR.Process I S) (right : U → A → PIR.Process I U)
    (law : ∀ state item, right (f state) item =
      (left state item).bind (fun result ↦ .done (f result))) (items : List A) (state : S) :
    Finite.fold right items (f state) =
      (Finite.fold left items state).bind (fun result ↦ .done (f result)) := by
  induction items generalizing state with
  | nil => rfl
  | cons item rest ih =>
    simp only [Finite.fold, law, PIR.Process.bind_assoc, PIR.Process.bind, ih]

end Zkc.Source.Structured.ProtocolEmbedding
