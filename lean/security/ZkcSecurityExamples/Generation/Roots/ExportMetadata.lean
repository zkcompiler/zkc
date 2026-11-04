module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:a97cec552c7c3eb40577b93eb195965de358090ac6b786cd718ffae4847ed51e", "sha256:9b4215eb172dd7fe907314e8e67a47018f55fca07693b1cda96da6538128699c", "sha256:c7698d09e1962c0b0c5d5f13ece4ce9fd307f824bab26e86bbd696e7932f84aa"),
  ("TwoSums", "sha256:e565f70ed061cdd7a411052abe0b918571fa7d0a0c8f8448599a5e40f82aff63", "sha256:292823554fb08e7c790831a90b8e6051def32e359c3acf01221d6f9abcfcf884", "sha256:b0616eb026871c4ba87d24296f187fb58bd56f7cc8a31dc9626d95540ecae5c1")]

end ZkcSecurity.Generation.Roots
