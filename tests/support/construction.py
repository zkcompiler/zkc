"""The plan the compiler produces from a source and a construction descriptor.

An artifact test states a source and the construction that realizes it, then
runs four files through the runtime and the Lean reference: the source, the
descriptor, the construction and the plan. Getting from the first two to the
last two is the same three steps every time — construct, take the common part
of what came back, compile that — and five tests were writing those steps out.
This is that route, as `lowering` is the route through MLIR.

The implementation selection is a parameter because it is a real choice: a test
that wants a named kernel chosen asks for it, and one that wants the compiler's
own choice does not. It is split in two because one of the five compiles two
plans from one construction, and asking for that with a flag would be worse
than letting it say so.

`prefix` is whatever the test puts in front of a file name, taken the way
`Journal.write` takes a name: the route is shared, where a test keeps its stages
is the test's own business. A test whose route differs is not expected to use
this — `oracle_construction` constructs from the text form and runs from the
JSON form, and says that better itself.
"""

PLAN = "physical.json"


def constructed(journal, compiler, source, descriptor, prefix):
    """Construct, keeping both what came back and the common part of it."""
    built = journal.json([compiler, "protocol-construct", source, descriptor])
    return (journal.write(f"{prefix}construction.json", built),
            journal.write(f"{prefix}common.json", built[2]))


def compiled(journal, compiler, common, prefix, selection=None, name=PLAN):
    """Compile a common part into a plan, under the implementations named."""
    options = [] if selection is None else ["--implementations=" + str(selection)]
    return journal.write(f"{prefix}{name}",
                         journal.json([compiler, "protocol-compile", common, *options]))


def constructed_plan(journal, compiler, source, descriptor, prefix, selection=None):
    """The four files an artifact run takes, in the order the runtime takes them."""
    construction, common = constructed(journal, compiler, source, descriptor, prefix)
    return [source, descriptor, construction,
            compiled(journal, compiler, common, prefix, selection)]
