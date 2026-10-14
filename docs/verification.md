# Verification scope

This source tree targets final round61 (`2ff7e75e9b6d626dc6c6243fa3d25fd179b34cf2`; manuscript SHA256 `d2a875c154db9ff913ec6b25cf38e8da134ca977f6a24fd9c036cd8873b1082a`). The inventory has 894 production and direct-verification Lean files, 893 production default targets, 17 numbered source statements, 16 manuscript proof blocks and 69 direct axiom queries.

| Check for this exact tree | Status |
| --- | --- |
| Independent statement, binder, definition and characterization review | PASS |
| Actual current proof-route and consumer review | PASS |
| Current applicability of the 25 registered / 22 Main assumptions | PASS |
| Standalone production build with zero compiler or linter warnings | PASS |
| All 69 fresh direct axiom reports | PASS |
| Current Main matching, Lean/NanoDa replay and complete environment queries | PASS |
| Hosted source CI | PENDING |
| Hosted comparator workflow | PENDING |

The release eligibility and comparator review records bind the exact source inventory. The required independent reviews have passed. A reviewed status-only metadata update preserves every production and verification-code identity used by the actual local runs. `check_public_inputs.py --static` checks inventory and assumptions only; it does not approve the source or establish a build result. Missing reviews or current comparator artifacts fail the verification workflows.

The 25 standard inputs stay external assumptions. Main must use exactly the selected 22, in addition to `propext`, `Classical.choice` and `Quot.sound`. Seven separately queried replacement/provider/consumer exports must use only these logical axioms. A source or literature audit does not prove an external input.

Earlier 885-file, 16-statement, 63-query checks belong to their historical source revisions. They provide no current build, review, comparator or hosted CI result. Badges are served by the actual GitHub workflows; successful outcomes must be tied to the exact public commit.

The local production check was a warm extension of authenticated objects built from this isolated public tree. No private project objects were used. Hosted workflows restore dependency artifacts only and compile fresh project objects.

The statement map covers the 17 numbered statements. The additional finite-volume radius bound mentioned in overview prose has a checked mathematical corollary argument; its separate ordinary Lean consumer remains pending and receives no formalization credit here.
