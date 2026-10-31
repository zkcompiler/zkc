module

public import Zkc.Source.Structured.ReferenceLaws
public import Zkc.Source.Structured.Template

@[expose] public section

/-! Exact nominal group helper laws. Recognition supplies body membership;
these laws supply the full mathematical outcome, for independent group and
scalar carriers. No sampling, knowledge or security premise is inferred. -/
set_option autoImplicit false
namespace Zkc.Protocols.Sigma.Source
open Zkc.Source Zkc.Source.Structured

structure Domains where
  group : String
  scalar : String
  deriving DecidableEq

def relationHelper (d : Domains) (name : String) : Helper :=
  ⟨name, .math, [.group d.group, .group d.group, .field d.scalar], [.boolean]⟩

def relationBody (d : Domains) :
    Region dialect (relationHelper d "").inputs [.boolean] :=
  .letOp (.groupScale d.group d.scalar) (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def relationLaw (model : DomainModel) (d : Domains) :
    ReferenceLaw model (relationHelper d "").inputs [.boolean] where
  body := relationBody d
  Requires _ _ := True
  reference args := .returned (.cons
    (decide (args.get (.there .here) = model.smul d.group d.scalar
      (args.get (.there (.there .here))) (args.get .here))) .nil)
  valid _ args _ := by
    match args with | .cons base (.cons point (.cons witness .nil)) => rfl

def responseHelper (scalar name : String) : Helper :=
  ⟨name, .math, [.field scalar, .field scalar, .field scalar], [.field scalar]⟩

def responseBody (scalar : String) :
    Region dialect (responseHelper scalar "").inputs [.field scalar] :=
  .letOp (.fieldMultiply scalar) (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil <|
  .letOp (.fieldAdd scalar) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def responseLaw (model : DomainModel) (scalar : String) :
    ReferenceLaw model (responseHelper scalar "").inputs [.field scalar] where
  body := responseBody scalar
  Requires _ _ := True
  reference args := .returned (.cons
    (args.get .here + args.get (.there .here) * args.get (.there (.there .here))) .nil)
  valid _ args _ := by
    match args with | .cons nonce (.cons challenge (.cons witness .nil)) => rfl

def equationHelper (d : Domains) (name : String) : Helper :=
  ⟨name, .math, [.group d.group, .group d.group, .group d.group,
    .field d.scalar, .field d.scalar], [.boolean]⟩

def equationBody (d : Domains) : Region dialect (equationHelper d "").inputs [.boolean] :=
  .letOp (.groupScale d.group d.scalar)
    (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupScale d.group d.scalar)
    (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupAdd d.group) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def equationLaw (model : DomainModel) (d : Domains) :
    ReferenceLaw model (equationHelper d "").inputs [.boolean] where
  body := equationBody d
  Requires _ _ := True
  reference args := .returned (.cons
    (decide (model.smul d.group d.scalar (args.get (.there (.there (.there (.there .here)))))
      (args.get .here) = args.get (.there (.there .here)) +
        model.smul d.group d.scalar (args.get (.there (.there (.there .here))))
          (args.get (.there .here)))) .nil)
  valid _ args _ := by
    match args with
    | .cons base (.cons point (.cons commitment (.cons challenge (.cons response .nil)))) => rfl

def independentHelper (d : Domains) (name : String) : Helper :=
  ⟨name, .math, [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar, .field d.scalar], [.boolean]⟩

def independentRelationBody (d : Domains) : Region dialect (independentHelper d "").inputs [.boolean] :=
  .letOp (.groupScale d.group d.scalar) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.groupScale d.group d.scalar) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def independentLaw (model : DomainModel) (d : Domains) :
    ReferenceLaw model (independentHelper d "").inputs [.boolean] where
  body := independentRelationBody d
  Requires _ _ := True
  reference args := .returned (.cons
    (decide (args.get (.there .here) = model.smul d.group d.scalar
      (args.get (.there (.there (.there (.there .here))))) (args.get .here)) &&
     decide (args.get (.there (.there (.there .here))) = model.smul d.group d.scalar
      (args.get (.there (.there (.there (.there (.there .here)))))) (args.get (.there (.there .here))))) .nil)
  valid _ args _ := by
    match args with
    | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint
        (.cons firstWitness (.cons secondWitness .nil))))) => rfl

def sharedHelper (d : Domains) (name : String) : Helper :=
  ⟨name, .math, [.group d.group, .group d.group, .group d.group, .group d.group, .field d.scalar], [.boolean]⟩

def sharedRelationBody (d : Domains) : Region dialect (sharedHelper d "").inputs [.boolean] :=
  .letOp (.groupScale d.group d.scalar) (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.groupScale d.group d.scalar) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.groupEqual d.group) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here .nil)) .nil <|
  .letOp .booleanAnd (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

def sharedLaw (model : DomainModel) (d : Domains) :
    ReferenceLaw model (sharedHelper d "").inputs [.boolean] where
  body := sharedRelationBody d
  Requires _ _ := True
  reference args := .returned (.cons
    (decide (args.get (.there .here) = model.smul d.group d.scalar
      (args.get (.there (.there (.there (.there .here))))) (args.get .here)) &&
     decide (args.get (.there (.there (.there .here))) = model.smul d.group d.scalar
      (args.get (.there (.there (.there (.there .here))))) (args.get (.there (.there .here))))) .nil)
  valid _ args _ := by
    match args with
    | .cons firstBase (.cons firstPoint (.cons secondBase (.cons secondPoint
        (.cons firstWitness .nil)))) => rfl

/-- Exact outcomes install in the complete linked helper table. Effectful
consumers use the same laws through `ReferenceLaw.invokeOn`. -/
theorem relation_invoke (model : DomainModel) (d : Domains) (name : String)
    (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (associated : BodyIn definitions (relationHelper d name) (relationBody d))
    (arguments : Values model.Value (relationHelper d name).inputs) :
    invoke (definitions.foldl (Evaluation.extendMeaningsOn model SiteObservations.closed) [])
      (relationHelper d name) arguments = primitiveOutcome ((relationLaw model d).reference arguments) :=
  ReferenceLaw.invoke (helper := relationHelper d name) (relationLaw model d)
    definitions linked associated arguments trivial

end Zkc.Protocols.Sigma.Source
