import FiniteAvalanches.External.BarlowMassonAdjacentPath
import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.BarlowMasson
open LatticeProb MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- One common conull witness supports the fully characterized finite paths for
every pair of lattice vertices; this uses the actual UST support export. -/
theorem squareLatticeUST_ae_genuine_paths :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField), ∃ hω : IsTree ω,
      ∀ (x y : Site 2) (p : (toGraph ω).Walk x y),
        (treePath ω hω x y = p ↔ p.IsPath) ∧
          ((treePath ω hω x y).support.toFinset : Set (Site 2)).Finite := by
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  exact ⟨hω.1, fun x y p => ⟨treePath_full_characterization ω hω.1 x y p,
    treePath_support_finite ω hω.1 x y⟩⟩

/-- The unconditional adjacent-path tail for the complementary dual UST field. -/
theorem dual_adjacent_path_euclidean_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site 2, (lattice 2).Adj x y →
      ∀ k : ℝ, 1 ≤ k →
        (squareLatticeUST : Measure EdgeField).real
          {ω | dualField ω ∈ treePathLeavesEuclidean x y k} ≤
          C * k ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨C, hC, htail⟩ :=
    FiniteAvalanches.External.BarlowMasson2011.adjacent_ust_path_euclidean_tail
  refine ⟨C, hC, ?_⟩
  intro x y hxy k hk
  have hmeasure : (squareLatticeUST : Measure EdgeField)
      {ω | dualField ω ∈ treePathLeavesEuclidean x y k} =
      (squareLatticeUST : Measure EdgeField) (treePathLeavesEuclidean x y k) := by
    have h := congrArg (fun μ : Measure EdgeField => μ (treePathLeavesEuclidean x y k))
      squareLatticeUST_dual_law
    rw [Measure.map_apply measurable_dualField
      (measurableSet_treePathLeavesEuclidean x y k)] at h
    exact h
  change ((squareLatticeUST : Measure EdgeField)
    {ω | dualField ω ∈ treePathLeavesEuclidean x y k}).toReal ≤ _
  rw [hmeasure]
  exact htail x y hxy k hk


end
end FiniteAvalanches.Trees.Lattice.BarlowMasson
