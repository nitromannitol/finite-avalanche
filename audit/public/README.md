# Current trust disclosure

The library uses Lean's `propext`, `Classical.choice` and `Quot.sound`, together
with the **26 external axioms** in [the current registry](../trusted-inputs.json).
Each entry contains its complete literal declaration source, primary citations
and source hashes, and every current semantic source file with complete bytes.
These literature inputs are assumptions, not newly proved Lean theorems.

[The projection record](projection.json) preserves the hash of the original
26-input registry and records every previously approved semantic pin revision.
[Review attestations](reviews/) explicitly project existing independent review
metadata. Their original report hashes are commitments: those private reports,
historical manifests, compiler receipts and downloaded primary texts are not
included and are not rechecked by these public scripts. No new mathematical
review or compilation is inferred from a hash commitment.

[The two proved inputs](proved-inputs.json) list the unchanged complete current
signatures, proof providers and exact consumers for arbitrary-site recurrence
hitting and killed/wired voltage. They are excluded from the axiom allowlist.
The fresh report gate requires all six replacement/provider/consumer exports
to use only the three logical axioms, even though other library exports may
use the 26 registered inputs.

[The compact current correspondence](current-statements.json) records all 16
numbered paper statements and their 15 proved anchors, with exact current paper
ranges, statement bytes and source hashes. The entire historical statement
manifest is not required or distributed here. Production Lean sources are
unchanged and are pinned by [the source inventory](source-files.json).

The public `check_public_inputs.registered_inputs(root)` API checks current
files and separately requires an independent approval of this public projection
and checker implementation. The [approval record](release-review.json) supplies
the actual verdict; normal CI and comparator preflight reject unless an actual
independent review approves the exact bindings. The internal `inspect_contents`
function checks content integrity only; production scripts do not use it as an
approval bypass.

After approval, `scripts/ci_build.sh` must build afresh with the pinned Lean and
dependencies and obtain all **4,737 fresh direct axiom reports**. The public
axiom checker rejects missing, duplicate or unexpected reports, warnings,
errors, proof holes, unauthorized axioms and nonprimitive proved replacements.
A historical log parser test is not a new public build.

[The comparator supplement](comparator-supplement.json) changes only the
registry disclosure view. It binds the unchanged full MAIN target, Challenge,
Solution, all six semantic payload files and all 26 permitted assertion types
to the new current-semantic identity. It carries forward existing pair-review
commitments and requires the separate public projection approval. A successful
preflight is not a sandboxed comparator or NanoDa result.
