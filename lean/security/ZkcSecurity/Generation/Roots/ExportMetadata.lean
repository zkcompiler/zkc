module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:c7bd8f9e5ecf095602373f1aea9324ff67dc00870477a4d72aafb35f4ff6fef1", "sha256:a5df066951a90844b8bc6ba8d5f395baedf9bb61ab607add8b631be7f08654ad", "sha256:52485f9a5a3ff1335ee0e00353f34fec71d268a59d26f29655291a5ed0ed5101"),
  ("TwoSums", "sha256:2dce173ee7e75348b151a0a921b5402960ac13c34dba46c91a14ee7ef7ed2dff", "sha256:502805d8613da1a8a3473d5bf24a6f3ea4a4e03a61abcf923f3c9a81d2fbd5ec", "sha256:8f9540dbdaf6c528a9a7d8eb51a2a46e92906fd776222adb1f59c3ffd625bba9")]

end ZkcSecurity.Generation.Roots
