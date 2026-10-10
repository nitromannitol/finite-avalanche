import FiniteAvalanches.Trees.Lattice.EuclideanPaths
import FiniteAvalanches.Trees.Lattice.InfiniteLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace FiniteAvalanches.External.BarlowMasson2011
open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Trees.Lattice.BarlowMasson

/-- Barlow--Masson, Lemma 2.6, upper bound (2011, arXiv:0912.4765v1 p.11 (2.12)),
translated to arbitrary adjacent sites. The same universal finite positive C
precedes all vertices and all real k≥1. Source balls are closed and Euclidean.
The path is the unique finite simple path in the actual lattice tree. -/
axiom adjacent_ust_path_euclidean_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site 2, (lattice 2).Adj x y →
      ∀ k : ℝ, 1 ≤ k →
        (squareLatticeUST : Measure EdgeField).real (treePathLeavesEuclidean x y k) ≤
          C * k ^ (-(1 / 3 : ℝ))

end FiniteAvalanches.External.BarlowMasson2011
