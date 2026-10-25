module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:c7bd8f9e5ecf095602373f1aea9324ff67dc00870477a4d72aafb35f4ff6fef1", "sha256:52fe282e78ac5b875db5c98b5780e0f4e57b00505ce6e99fdc2b24a75dc398f9", "sha256:5a57b102cd46cb4fc6e5e9f1aa86f59c88e726a6df18b5d5405041a146f9f7e3"),
  ("TwoSums", "sha256:2dce173ee7e75348b151a0a921b5402960ac13c34dba46c91a14ee7ef7ed2dff", "sha256:acdc83f8b481571122cc695d94b43563d9bdf2999f3bfb308fc5badefb4b84ff", "sha256:c4aeab47c47c6d1297c475b16826485dab6edc8ceeba4ddfa6b0923bead527f8")]

end ZkcSecurity.Generation.Roots
