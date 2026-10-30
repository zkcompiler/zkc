module

public import Zkc.Source.Structured.MultilinearBodies

@[expose] public section

/-! Dependency selections for retained multilinear source views. The reference
library checks the complete typed bodies; these strings do not select formulas. -/
namespace ZkcExamples.Structured.MultilinearSourceBindings
open Zkc.Source.Structured

def common : MultilinearBodies.Bindings where
  less := "s3h7a6b637h696e64696365734h6c657373"
  rows := "s3h7a6b6311h6d756c74696c696e6561724h726f7773"
  shape := "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"
  table := "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"
  halves := "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"
  interpolate := "zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5"
  first := "zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d"
  step := "zkl_195a79478f48dffc2a6917273d8317df0fabae786920a46fa2ac6b2737144299"
  foldStep := "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_body"
  foldDomain := "finite_zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2_s0_domain"
  foldWrapper := "zkl_c2d42dbaddef5ba2c1cc53ef9331fa1a1265965e933e58a876b38cd6b3a303b2"
  restrictPrefix := "zkl_96cd7ea616c46001ac0fa39e06ab5b8042d6d50ce126ce52a57cd4f1fd0ed9be"
  values := "zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33"
  dimension := "zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94"
  width := "zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275"
  sums := "zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6"
  checkTable := "zkl_967e003dd39c9e1730d1e9e543081e08e351228ff07f85fb14e1e88dbded8a99"
  interpolation := ""
  callback := ""
  collection := ""
  collectionDomain := ""
  fold := ""
  valuesRealization := ""

/-- Shared private-admission selection in the two retained Sumcheck libraries. -/
def sumcheck : MultilinearBodies.Bindings :=
  { common with
    interpolation := "_mathematical_admission_1"
    callback := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_body"
    collection := "_finite_admission_0"
    collectionDomain := "zkl_map_fa2ed749b4391bd0768410c62902b36b118ac0c5cac2161084dec0ccfc709d8a_domain"
    fold := "_finite_admission_3"
    valuesRealization := "_mathematical_admission_2" }

end ZkcExamples.Structured.MultilinearSourceBindings
