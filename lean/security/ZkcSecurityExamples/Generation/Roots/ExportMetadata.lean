module

@[expose] public section

/-! Generated SHA-256 identities of exact retained export and identity bytes.
Refresh and check with lean/checks/check_subject_roots.py --exports DIRECTORY.
Current participant exports are independently checked against the selected pair. -/
namespace ZkcSecurity.Generation.Roots

def exportDigests : List (String × String × String × String) := [
  ("SmallSumcheck", "sha256:2570cea125278771a8451ddc403d67d3cd7080315e457c4adc175a89508e1356", "sha256:5592d46a92e6c1df4f875dcee0566bb3e5bba510580b3bd2de6e35e511fbee4d", "sha256:319f01c59dea31eafdcc8512da7a195a34173c5ffbfd558c91d56b9093ba3108"),
  ("TwoSums", "sha256:d599edea4215f7f3349457a06480c86d19cb7492ed5f0707264e9159367dc939", "sha256:13fa19f0bd32f0e4ac65649705b74d2b4844368ab5cdc210c789c84c0bd3e77d", "sha256:60fa4320e8a4e3b5fc39cdbdd68fc181c7128971935ececba23be11dbc18db35")]

end ZkcSecurity.Generation.Roots
