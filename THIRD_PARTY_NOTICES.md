# Third-party source notices

The mathematical definitions use the following Mathlib source files from the pinned dependency:

- `Mathlib/Logic/Relation.lean`
- `Mathlib/Data/Finset/BooleanAlgebra.lean`
- `Mathlib/Data/Finset/Erase.lean`
- `Mathlib/Topology/Connected/Clopen.lean`

These files are fetched through the dependency pin in `lake-manifest.json`. Mathlib retains its original copyright and author notices. Its source is [Mathlib](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997), distributed under [Apache License 2.0](LICENSES/Apache-2.0.txt).

## Copied source files

The following files are copied into this repository with attribution. Each file starts with a
header naming its source repository, module path and commit, and the changes made here.

- **Álvaro Begué, [schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean/tree/05a43d29cde026618777db3d4e4316204ccca237)**,
  commit `05a43d29cde026618777db3d4e4316204ccca237`: the 128 modules under
  `FiniteAvalanches/Support/Schoenflies/`, copied from `Schoenflies/`. They are distributed under
  the [Apache License 2.0](FiniteAvalanches/Support/Schoenflies/LICENSE), whose text is kept next to
  them. Each header keeps the upstream copyright and author lines and states that the file was
  modified: comments removed, imports renamed, and explicit binders added in six files.
- **Leonardo Bonanno, [lean-formalizations](https://github.com/leobon12/lean-formalizations/tree/31e748330ee154d5f41537c4b01f71b8a5510c2d)**,
  commit `31e748330ee154d5f41537c4b01f71b8a5510c2d`: six modules under
  `FiniteAvalanches/Support/Plane/`, copied with attribution to Leonardo Bonanno:
  - `Disconnect.lean` (the definition `Disconnects` from `LQGMetric/Topo/Disconnect.lean`);
  - `PlanarCore.lean` (from `MatedCRTHarmonic/Topology/PlanarCore.lean`);
  - `TopoDegree.lean`, `TopoEilenberg.lean`, `TopoJaniszewski.lean` and `TopoSep.lean` (from the
    files of the same names in `QuantumZipper/Proofs/Complex/`).

  The upstream repository does not state a licence, and none is claimed here.
- **[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability/tree/0b6994229ccf31047ae7b654ecbec59496594700)**,
  the library this project depends on, commit `0b6994229ccf31047ae7b654ecbec59496594700`,
  distributed under the Apache License 2.0:
  `FiniteAvalanches/Support/Plane/FinitePointComplement.lean`,
  `FiniteAvalanches/Support/Plane/LocalFaceIncidence.lean`,
  `FiniteAvalanches/Wilson/LoopErasureComposition.lean` and
  `FiniteAvalanches/Wilson/CyclePopping/{Basic,Erasure,Trace}.lean`.

Other dependencies and verification tools are fetched from the source repositories and revisions recorded in `lake-manifest.json` and `audit/comparator-tool-pins.json`. No third-party paper or book PDF is included.
