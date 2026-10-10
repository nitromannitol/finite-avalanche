# Third-party source notices

Four unmodified Mathlib source files are included as part of the mathematical definitions pinned by the external-input registry:

- `Mathlib/Logic/Relation.lean`
- `Mathlib/Data/Finset/BooleanAlgebra.lean`
- `Mathlib/Data/Finset/Erase.lean`
- `Mathlib/Topology/Connected/Clopen.lean`

They are mirrored under `audit/tree-complement-dictionary-7c/meaning/Mathlib/`, with a `.txt` extension. Each retains its original copyright and author notice. Their source is [Mathlib](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997), distributed under [Apache License 2.0](LICENSES/Apache-2.0.txt).

Other dependencies and verification tools are fetched from the source repositories and revisions recorded in `lake-manifest.json` and `audit/comparator-tool-pins.json`; their sources are not vendored by this release. No third-party paper or book PDF is included.
