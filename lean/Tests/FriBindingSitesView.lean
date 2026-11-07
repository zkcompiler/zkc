module

public import Tests.FriBindingSitesData
public import ZkcExamples.Structured.FriSourceViews

@[expose] public section

/-! Admit the second client in phases. Only its new root needs its own typed body. -/
namespace Tests.FriBindingSitesView
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured.FriSourceBodies
def doubleSignature : ProtocolSignature where
  name := "s7h6578616d706c653h467269"
  roles := ["role00000000", "role00000001"]
  inputs := [(.vector "koala-bear.ext8-binomial3"), (.field "koala-bear.ext8-binomial3"), .index, .index, (.service "random.koala-bear.ext8-binomial3/0")]
  outputs := [.boolean, .boolean]
  inputScopes := [[0], [0, 1], [0, 1], [0, 1], [1]]
  outputScopes := [[1], [1]]

def doubleBody : Region protocolDialect doubleSignature.inputs doubleSignature.outputs :=
  .letOp (.mark "label_6c656674") .nil .nil <|
  .letOp (.protocolApply protocol5Signature [0, 1] "label_6c656674") (.cons .here (.cons (.there .here) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)))))) .nil <|
  .letOp (.mark "label_7269676874") .nil .nil <|
  .letOp (.protocolApply protocol5Signature [0, 1] "label_7269676874") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))) .nil <|
  .ret (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil))

set_option smartUnfolding false

structured_views FriBindingSitesData.snapshot
  helpers [helper0, helper1, helper2, helper3, helper4, helper5, helper6, helper7, helper8, helper9, helper10, helper11, helper12, formula, helper14, helper15, helper16, helper17, helper18, helper19, helper20, helper21, helper22, helper23, helper24, helper25, helper26, helper27, helper28, helper29, helper30, helper31, helper32, helper33, helper34, helper35, helper36]
  protocols [protocol0, protocol1, protocol2, protocol3, protocol4, protocol5, double]

theorem admitted : check FriBindingSitesData.snapshot = .ok program := kernel_admission

end Tests.FriBindingSitesView
