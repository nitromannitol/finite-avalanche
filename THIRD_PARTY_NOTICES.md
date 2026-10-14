# Third-party source notices

The mathematical definitions use the following Mathlib source files from the pinned dependency:

- `Mathlib/Logic/Relation.lean`
- `Mathlib/Data/Finset/BooleanAlgebra.lean`
- `Mathlib/Data/Finset/Erase.lean`
- `Mathlib/Topology/Connected/Clopen.lean`

These files are fetched through the dependency pin in `lake-manifest.json`; no mirrors are vendored by this projection. Mathlib retains its original copyright and author notices. Its source is [Mathlib](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997), distributed under [Apache License 2.0](LICENSES/Apache-2.0.txt).

Other dependencies and verification tools are fetched from the source repositories and revisions recorded in `lake-manifest.json` and `audit/comparator-tool-pins.json`; their sources are not vendored by this release. No third-party paper or book PDF is included.
