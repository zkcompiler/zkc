# Optional formal fixture support

`variant_codec.py` constructs independent semantic trees used by
`formal/checks/variant_cli.py`. It was retained here when the compiler's old
Frontend fixtures were retired. `tests/run.py lean` supplies this directory on
`PYTHONPATH`; the default native test/build graph does not import it. This is
fixture construction for the independent Lean research package, not a native
program reader or a compatibility implementation.

`check_cli.py` checks usage refusal for the standalone table research tools,
malformed requirement envelopes, and the independent iteration reference's
return, suspension and stopped-effect records. These tools are not called by
native execution tests.
