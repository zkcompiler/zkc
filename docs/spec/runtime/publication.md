# File admission and publication

This native contract covers Entry CLI files and reports. The [Entry guide](../../runtime/entries.md)
explains commands; [Entry calls](entries.md) own their logical inputs.

## Reports and returned values

Standard output contains a structured status report. It retains resource usage,
attempt decisions, stops, cleanup and publication state. It omits returned values
and proof payloads. Exit status is zero only after complete execution, cleanup
and requested publication.

Use `--results=FILE` to publish returned logical values. Run files contain a
`roles` map; proof files contain `values` for the invoked participant. Both use
`zkc.entry-outputs/0`. Encoding honors admitted native capacity and a 16 MiB whole
file limit. Non-Wire private results cannot be serialized.

## File admission

Entry input documents share a 16 MiB byte limit and a 200,000-node allowance
including object keys per invocation; each document has depth at most 72. Decoding rejects duplicate keys, unknown record
fields, trailing documents and numeric values outside unsigned 64-bit naturals.
The application authority file is bounded by 64 KiB.
[Entry file adapters](entries.md#file-adapters-and-rust-bindings) define request,
value and `zkc.entry-setups/0` authority schemas.

All configured input and authority paths name bounded regular files. Explicit authority, package and policy paths may resolve symlinks to regular
files. On Unix, Entry JSON document names and references refuse final symlinks; confined
reference traversal also refuses intermediate symlinks. FIFOs, devices and
other nonregular inputs refuse. Byte-slice APIs remain available for applications that own their
transport. Compile sources and assets also require regular files, with capture
limits enforced by the compiler.

## Output publication

Output paths must differ from each other and all input/configuration paths,
including opened native-value and prover-key references. Descriptor identities
remain protected after their original path is replaced. Existing symlink outputs and nonregular
destinations refuse. Canonical directory aliases and, on Unix, existing hardlink aliases
also refuse. Execution destination parents must already exist. Project and input initialization
create their destination directories and publish without replacing existing files. The plan is rechecked
before publication. These are trusted configuration checks; concurrent hostile
filesystem mutation is outside this contract.

The Host encodes every requested output and writes and syncs all temporary files
before replacing any destination. Preflight, encoding and staging failures leave
prior files intact. On Unix, published files use mode `0600`, including replacements;
previous destination permissions are not preserved. Publication atomically replaces
each file, in order:
proof followed by optional results. This is per-file publication, not a multi-file
transaction. A later replacement can fail after the proof was published. The
report retains `proof_published: true`, a `publication.published` list, the
`publication.failed` output name, and execution observations. Staging refusal has
an empty published list. Publication errors never trigger an automatic rerun;
these operations do not promise crash durability of directory entries.
