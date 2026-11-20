/-
Copied from Lattice-Probability (https://github.com/nitromannitol/Lattice-Probability), module
`LatticeProb/Walk/KilledGreenPlanarLower.lean`, commit 99cfc20cb60d38c947523641e991a84350e77309.
Changes: only the lemma `abs_coord_le_euclidNorm` is copied, the rest of the module is omitted;
the imports are reduced to `LatticeProb.Walk.Ball`; namespace `LatticeProb` renamed to
`FiniteAvalanches.Walk`, with `open LatticeProb` added; the module docstring is replaced.
-/
import LatticeProb.Walk.Ball

/-!
# Coordinates and the Euclidean norm of a planar site

Each coordinate of a site of `ℤ²` is at most its Euclidean norm in absolute value.
-/

namespace FiniteAvalanches.Walk
open LatticeProb

/-- Each coordinate of a site is at most its Euclidean norm in absolute value. -/
theorem abs_coord_le_euclidNorm (x : Site 2) (i : Fin 2) :
    |((x i : ℤ) : ℝ)| ≤ euclidNorm x := by
  rw [euclidNorm, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j : Fin 2 => ((x j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

end FiniteAvalanches.Walk
