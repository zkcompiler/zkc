"""Records of what is proved: declaration records, the claims ledger and assurance reports.

`declarations` runs the Lean emitter and reads its output, `ledger` checks the
claims ledger against the records and renders the "What is proved" table, and
`reports` joins subject manifests, records, the registry and pipeline evidence
into `zkc.assurance-report/0` documents. `check_records.py` is the command.
"""
